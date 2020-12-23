%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:20 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 201 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  205 ( 631 expanded)
%              Number of equality atoms :  165 ( 521 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f25])).

fof(f49,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f53])).

fof(f55,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f56,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f68,plain,(
    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f49,f51,f56,f56,f56])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f42,f51,f48,f56])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f69,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f64])).

fof(f70,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f69])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f54])).

fof(f75,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f54])).

fof(f73,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f66])).

fof(f74,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f73])).

fof(f50,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_787,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_10,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_216,plain,
    ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_26282,plain,
    ( r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_216])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_346,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
    | sK2 = X0
    | sK2 = X1
    | sK2 = X2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_347,plain,
    ( sK2 = X0
    | sK2 = X1
    | sK2 = X2
    | r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_349,plain,
    ( sK2 = sK1
    | r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_347])).

cnf(c_87,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_304,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_305,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_304])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_20,plain,
    ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17,plain,
    ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_14,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_26282,c_349,c_305,c_20,c_17,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:54:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 8.08/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.08/1.49  
% 8.08/1.49  ------  iProver source info
% 8.08/1.49  
% 8.08/1.49  git: date: 2020-06-30 10:37:57 +0100
% 8.08/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.08/1.49  git: non_committed_changes: false
% 8.08/1.49  git: last_make_outside_of_git: false
% 8.08/1.49  
% 8.08/1.49  ------ 
% 8.08/1.49  
% 8.08/1.49  ------ Input Options
% 8.08/1.49  
% 8.08/1.49  --out_options                           all
% 8.08/1.49  --tptp_safe_out                         true
% 8.08/1.49  --problem_path                          ""
% 8.08/1.49  --include_path                          ""
% 8.08/1.49  --clausifier                            res/vclausify_rel
% 8.08/1.49  --clausifier_options                    --mode clausify
% 8.08/1.49  --stdin                                 false
% 8.08/1.49  --stats_out                             sel
% 8.08/1.49  
% 8.08/1.49  ------ General Options
% 8.08/1.49  
% 8.08/1.49  --fof                                   false
% 8.08/1.49  --time_out_real                         604.99
% 8.08/1.49  --time_out_virtual                      -1.
% 8.08/1.49  --symbol_type_check                     false
% 8.08/1.49  --clausify_out                          false
% 8.08/1.49  --sig_cnt_out                           false
% 8.08/1.49  --trig_cnt_out                          false
% 8.08/1.49  --trig_cnt_out_tolerance                1.
% 8.08/1.49  --trig_cnt_out_sk_spl                   false
% 8.08/1.49  --abstr_cl_out                          false
% 8.08/1.49  
% 8.08/1.49  ------ Global Options
% 8.08/1.49  
% 8.08/1.49  --schedule                              none
% 8.08/1.49  --add_important_lit                     false
% 8.08/1.49  --prop_solver_per_cl                    1000
% 8.08/1.49  --min_unsat_core                        false
% 8.08/1.49  --soft_assumptions                      false
% 8.08/1.49  --soft_lemma_size                       3
% 8.08/1.49  --prop_impl_unit_size                   0
% 8.08/1.49  --prop_impl_unit                        []
% 8.08/1.49  --share_sel_clauses                     true
% 8.08/1.49  --reset_solvers                         false
% 8.08/1.49  --bc_imp_inh                            [conj_cone]
% 8.08/1.49  --conj_cone_tolerance                   3.
% 8.08/1.49  --extra_neg_conj                        none
% 8.08/1.49  --large_theory_mode                     true
% 8.08/1.49  --prolific_symb_bound                   200
% 8.08/1.49  --lt_threshold                          2000
% 8.08/1.49  --clause_weak_htbl                      true
% 8.08/1.49  --gc_record_bc_elim                     false
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing Options
% 8.08/1.49  
% 8.08/1.49  --preprocessing_flag                    true
% 8.08/1.49  --time_out_prep_mult                    0.1
% 8.08/1.49  --splitting_mode                        input
% 8.08/1.49  --splitting_grd                         true
% 8.08/1.49  --splitting_cvd                         false
% 8.08/1.49  --splitting_cvd_svl                     false
% 8.08/1.49  --splitting_nvd                         32
% 8.08/1.49  --sub_typing                            true
% 8.08/1.49  --prep_gs_sim                           false
% 8.08/1.49  --prep_unflatten                        true
% 8.08/1.49  --prep_res_sim                          true
% 8.08/1.49  --prep_upred                            true
% 8.08/1.49  --prep_sem_filter                       exhaustive
% 8.08/1.49  --prep_sem_filter_out                   false
% 8.08/1.49  --pred_elim                             false
% 8.08/1.49  --res_sim_input                         true
% 8.08/1.49  --eq_ax_congr_red                       true
% 8.08/1.49  --pure_diseq_elim                       true
% 8.08/1.49  --brand_transform                       false
% 8.08/1.49  --non_eq_to_eq                          false
% 8.08/1.49  --prep_def_merge                        true
% 8.08/1.49  --prep_def_merge_prop_impl              false
% 8.08/1.49  --prep_def_merge_mbd                    true
% 8.08/1.49  --prep_def_merge_tr_red                 false
% 8.08/1.49  --prep_def_merge_tr_cl                  false
% 8.08/1.49  --smt_preprocessing                     true
% 8.08/1.49  --smt_ac_axioms                         fast
% 8.08/1.49  --preprocessed_out                      false
% 8.08/1.49  --preprocessed_stats                    false
% 8.08/1.49  
% 8.08/1.49  ------ Abstraction refinement Options
% 8.08/1.49  
% 8.08/1.49  --abstr_ref                             []
% 8.08/1.49  --abstr_ref_prep                        false
% 8.08/1.49  --abstr_ref_until_sat                   false
% 8.08/1.49  --abstr_ref_sig_restrict                funpre
% 8.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.49  --abstr_ref_under                       []
% 8.08/1.49  
% 8.08/1.49  ------ SAT Options
% 8.08/1.49  
% 8.08/1.49  --sat_mode                              false
% 8.08/1.49  --sat_fm_restart_options                ""
% 8.08/1.49  --sat_gr_def                            false
% 8.08/1.49  --sat_epr_types                         true
% 8.08/1.49  --sat_non_cyclic_types                  false
% 8.08/1.49  --sat_finite_models                     false
% 8.08/1.49  --sat_fm_lemmas                         false
% 8.08/1.49  --sat_fm_prep                           false
% 8.08/1.49  --sat_fm_uc_incr                        true
% 8.08/1.49  --sat_out_model                         small
% 8.08/1.49  --sat_out_clauses                       false
% 8.08/1.49  
% 8.08/1.49  ------ QBF Options
% 8.08/1.49  
% 8.08/1.49  --qbf_mode                              false
% 8.08/1.49  --qbf_elim_univ                         false
% 8.08/1.49  --qbf_dom_inst                          none
% 8.08/1.49  --qbf_dom_pre_inst                      false
% 8.08/1.49  --qbf_sk_in                             false
% 8.08/1.49  --qbf_pred_elim                         true
% 8.08/1.49  --qbf_split                             512
% 8.08/1.49  
% 8.08/1.49  ------ BMC1 Options
% 8.08/1.49  
% 8.08/1.49  --bmc1_incremental                      false
% 8.08/1.49  --bmc1_axioms                           reachable_all
% 8.08/1.49  --bmc1_min_bound                        0
% 8.08/1.49  --bmc1_max_bound                        -1
% 8.08/1.49  --bmc1_max_bound_default                -1
% 8.08/1.49  --bmc1_symbol_reachability              true
% 8.08/1.49  --bmc1_property_lemmas                  false
% 8.08/1.49  --bmc1_k_induction                      false
% 8.08/1.49  --bmc1_non_equiv_states                 false
% 8.08/1.49  --bmc1_deadlock                         false
% 8.08/1.49  --bmc1_ucm                              false
% 8.08/1.49  --bmc1_add_unsat_core                   none
% 8.08/1.49  --bmc1_unsat_core_children              false
% 8.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.49  --bmc1_out_stat                         full
% 8.08/1.49  --bmc1_ground_init                      false
% 8.08/1.49  --bmc1_pre_inst_next_state              false
% 8.08/1.49  --bmc1_pre_inst_state                   false
% 8.08/1.49  --bmc1_pre_inst_reach_state             false
% 8.08/1.49  --bmc1_out_unsat_core                   false
% 8.08/1.49  --bmc1_aig_witness_out                  false
% 8.08/1.49  --bmc1_verbose                          false
% 8.08/1.49  --bmc1_dump_clauses_tptp                false
% 8.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.49  --bmc1_dump_file                        -
% 8.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.49  --bmc1_ucm_extend_mode                  1
% 8.08/1.49  --bmc1_ucm_init_mode                    2
% 8.08/1.49  --bmc1_ucm_cone_mode                    none
% 8.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.49  --bmc1_ucm_relax_model                  4
% 8.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.49  --bmc1_ucm_layered_model                none
% 8.08/1.49  --bmc1_ucm_max_lemma_size               10
% 8.08/1.49  
% 8.08/1.49  ------ AIG Options
% 8.08/1.49  
% 8.08/1.49  --aig_mode                              false
% 8.08/1.49  
% 8.08/1.49  ------ Instantiation Options
% 8.08/1.49  
% 8.08/1.49  --instantiation_flag                    true
% 8.08/1.49  --inst_sos_flag                         false
% 8.08/1.49  --inst_sos_phase                        true
% 8.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel_side                     num_symb
% 8.08/1.49  --inst_solver_per_active                1400
% 8.08/1.49  --inst_solver_calls_frac                1.
% 8.08/1.49  --inst_passive_queue_type               priority_queues
% 8.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.49  --inst_passive_queues_freq              [25;2]
% 8.08/1.49  --inst_dismatching                      true
% 8.08/1.49  --inst_eager_unprocessed_to_passive     true
% 8.08/1.49  --inst_prop_sim_given                   true
% 8.08/1.49  --inst_prop_sim_new                     false
% 8.08/1.49  --inst_subs_new                         false
% 8.08/1.49  --inst_eq_res_simp                      false
% 8.08/1.49  --inst_subs_given                       false
% 8.08/1.49  --inst_orphan_elimination               true
% 8.08/1.49  --inst_learning_loop_flag               true
% 8.08/1.49  --inst_learning_start                   3000
% 8.08/1.49  --inst_learning_factor                  2
% 8.08/1.49  --inst_start_prop_sim_after_learn       3
% 8.08/1.49  --inst_sel_renew                        solver
% 8.08/1.49  --inst_lit_activity_flag                true
% 8.08/1.49  --inst_restr_to_given                   false
% 8.08/1.49  --inst_activity_threshold               500
% 8.08/1.49  --inst_out_proof                        true
% 8.08/1.49  
% 8.08/1.49  ------ Resolution Options
% 8.08/1.49  
% 8.08/1.49  --resolution_flag                       true
% 8.08/1.49  --res_lit_sel                           adaptive
% 8.08/1.49  --res_lit_sel_side                      none
% 8.08/1.49  --res_ordering                          kbo
% 8.08/1.49  --res_to_prop_solver                    active
% 8.08/1.49  --res_prop_simpl_new                    false
% 8.08/1.49  --res_prop_simpl_given                  true
% 8.08/1.49  --res_passive_queue_type                priority_queues
% 8.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.49  --res_passive_queues_freq               [15;5]
% 8.08/1.49  --res_forward_subs                      full
% 8.08/1.49  --res_backward_subs                     full
% 8.08/1.49  --res_forward_subs_resolution           true
% 8.08/1.49  --res_backward_subs_resolution          true
% 8.08/1.49  --res_orphan_elimination                true
% 8.08/1.49  --res_time_limit                        2.
% 8.08/1.49  --res_out_proof                         true
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Options
% 8.08/1.49  
% 8.08/1.49  --superposition_flag                    true
% 8.08/1.49  --sup_passive_queue_type                priority_queues
% 8.08/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.49  --sup_passive_queues_freq               [1;4]
% 8.08/1.49  --demod_completeness_check              fast
% 8.08/1.49  --demod_use_ground                      true
% 8.08/1.49  --sup_to_prop_solver                    passive
% 8.08/1.49  --sup_prop_simpl_new                    true
% 8.08/1.49  --sup_prop_simpl_given                  true
% 8.08/1.49  --sup_fun_splitting                     false
% 8.08/1.49  --sup_smt_interval                      50000
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Simplification Setup
% 8.08/1.49  
% 8.08/1.49  --sup_indices_passive                   []
% 8.08/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_full_bw                           [BwDemod]
% 8.08/1.49  --sup_immed_triv                        [TrivRules]
% 8.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_immed_bw_main                     []
% 8.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  
% 8.08/1.49  ------ Combination Options
% 8.08/1.49  
% 8.08/1.49  --comb_res_mult                         3
% 8.08/1.49  --comb_sup_mult                         2
% 8.08/1.49  --comb_inst_mult                        10
% 8.08/1.49  
% 8.08/1.49  ------ Debug Options
% 8.08/1.49  
% 8.08/1.49  --dbg_backtrace                         false
% 8.08/1.49  --dbg_dump_prop_clauses                 false
% 8.08/1.49  --dbg_dump_prop_clauses_file            -
% 8.08/1.49  --dbg_out_stat                          false
% 8.08/1.49  ------ Parsing...
% 8.08/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.08/1.49  ------ Proving...
% 8.08/1.49  ------ Problem Properties 
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  clauses                                 16
% 8.08/1.49  conjectures                             2
% 8.08/1.49  EPR                                     1
% 8.08/1.49  Horn                                    14
% 8.08/1.49  unary                                   11
% 8.08/1.49  binary                                  0
% 8.08/1.49  lits                                    29
% 8.08/1.49  lits eq                                 21
% 8.08/1.49  fd_pure                                 0
% 8.08/1.49  fd_pseudo                               0
% 8.08/1.49  fd_cond                                 0
% 8.08/1.49  fd_pseudo_cond                          4
% 8.08/1.49  AC symbols                              0
% 8.08/1.49  
% 8.08/1.49  ------ Input Options Time Limit: Unbounded
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ 
% 8.08/1.49  Current options:
% 8.08/1.49  ------ 
% 8.08/1.49  
% 8.08/1.49  ------ Input Options
% 8.08/1.49  
% 8.08/1.49  --out_options                           all
% 8.08/1.49  --tptp_safe_out                         true
% 8.08/1.49  --problem_path                          ""
% 8.08/1.49  --include_path                          ""
% 8.08/1.49  --clausifier                            res/vclausify_rel
% 8.08/1.49  --clausifier_options                    --mode clausify
% 8.08/1.49  --stdin                                 false
% 8.08/1.49  --stats_out                             sel
% 8.08/1.49  
% 8.08/1.49  ------ General Options
% 8.08/1.49  
% 8.08/1.49  --fof                                   false
% 8.08/1.49  --time_out_real                         604.99
% 8.08/1.49  --time_out_virtual                      -1.
% 8.08/1.49  --symbol_type_check                     false
% 8.08/1.49  --clausify_out                          false
% 8.08/1.49  --sig_cnt_out                           false
% 8.08/1.49  --trig_cnt_out                          false
% 8.08/1.49  --trig_cnt_out_tolerance                1.
% 8.08/1.49  --trig_cnt_out_sk_spl                   false
% 8.08/1.49  --abstr_cl_out                          false
% 8.08/1.49  
% 8.08/1.49  ------ Global Options
% 8.08/1.49  
% 8.08/1.49  --schedule                              none
% 8.08/1.49  --add_important_lit                     false
% 8.08/1.49  --prop_solver_per_cl                    1000
% 8.08/1.49  --min_unsat_core                        false
% 8.08/1.49  --soft_assumptions                      false
% 8.08/1.49  --soft_lemma_size                       3
% 8.08/1.49  --prop_impl_unit_size                   0
% 8.08/1.49  --prop_impl_unit                        []
% 8.08/1.49  --share_sel_clauses                     true
% 8.08/1.49  --reset_solvers                         false
% 8.08/1.49  --bc_imp_inh                            [conj_cone]
% 8.08/1.49  --conj_cone_tolerance                   3.
% 8.08/1.49  --extra_neg_conj                        none
% 8.08/1.49  --large_theory_mode                     true
% 8.08/1.49  --prolific_symb_bound                   200
% 8.08/1.49  --lt_threshold                          2000
% 8.08/1.49  --clause_weak_htbl                      true
% 8.08/1.49  --gc_record_bc_elim                     false
% 8.08/1.49  
% 8.08/1.49  ------ Preprocessing Options
% 8.08/1.49  
% 8.08/1.49  --preprocessing_flag                    true
% 8.08/1.49  --time_out_prep_mult                    0.1
% 8.08/1.49  --splitting_mode                        input
% 8.08/1.49  --splitting_grd                         true
% 8.08/1.49  --splitting_cvd                         false
% 8.08/1.49  --splitting_cvd_svl                     false
% 8.08/1.49  --splitting_nvd                         32
% 8.08/1.49  --sub_typing                            true
% 8.08/1.49  --prep_gs_sim                           false
% 8.08/1.49  --prep_unflatten                        true
% 8.08/1.49  --prep_res_sim                          true
% 8.08/1.49  --prep_upred                            true
% 8.08/1.49  --prep_sem_filter                       exhaustive
% 8.08/1.49  --prep_sem_filter_out                   false
% 8.08/1.49  --pred_elim                             false
% 8.08/1.49  --res_sim_input                         true
% 8.08/1.49  --eq_ax_congr_red                       true
% 8.08/1.49  --pure_diseq_elim                       true
% 8.08/1.49  --brand_transform                       false
% 8.08/1.49  --non_eq_to_eq                          false
% 8.08/1.49  --prep_def_merge                        true
% 8.08/1.49  --prep_def_merge_prop_impl              false
% 8.08/1.49  --prep_def_merge_mbd                    true
% 8.08/1.49  --prep_def_merge_tr_red                 false
% 8.08/1.49  --prep_def_merge_tr_cl                  false
% 8.08/1.49  --smt_preprocessing                     true
% 8.08/1.49  --smt_ac_axioms                         fast
% 8.08/1.49  --preprocessed_out                      false
% 8.08/1.49  --preprocessed_stats                    false
% 8.08/1.49  
% 8.08/1.49  ------ Abstraction refinement Options
% 8.08/1.49  
% 8.08/1.49  --abstr_ref                             []
% 8.08/1.49  --abstr_ref_prep                        false
% 8.08/1.49  --abstr_ref_until_sat                   false
% 8.08/1.49  --abstr_ref_sig_restrict                funpre
% 8.08/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.08/1.49  --abstr_ref_under                       []
% 8.08/1.49  
% 8.08/1.49  ------ SAT Options
% 8.08/1.49  
% 8.08/1.49  --sat_mode                              false
% 8.08/1.49  --sat_fm_restart_options                ""
% 8.08/1.49  --sat_gr_def                            false
% 8.08/1.49  --sat_epr_types                         true
% 8.08/1.49  --sat_non_cyclic_types                  false
% 8.08/1.49  --sat_finite_models                     false
% 8.08/1.49  --sat_fm_lemmas                         false
% 8.08/1.49  --sat_fm_prep                           false
% 8.08/1.49  --sat_fm_uc_incr                        true
% 8.08/1.49  --sat_out_model                         small
% 8.08/1.49  --sat_out_clauses                       false
% 8.08/1.49  
% 8.08/1.49  ------ QBF Options
% 8.08/1.49  
% 8.08/1.49  --qbf_mode                              false
% 8.08/1.49  --qbf_elim_univ                         false
% 8.08/1.49  --qbf_dom_inst                          none
% 8.08/1.49  --qbf_dom_pre_inst                      false
% 8.08/1.49  --qbf_sk_in                             false
% 8.08/1.49  --qbf_pred_elim                         true
% 8.08/1.49  --qbf_split                             512
% 8.08/1.49  
% 8.08/1.49  ------ BMC1 Options
% 8.08/1.49  
% 8.08/1.49  --bmc1_incremental                      false
% 8.08/1.49  --bmc1_axioms                           reachable_all
% 8.08/1.49  --bmc1_min_bound                        0
% 8.08/1.49  --bmc1_max_bound                        -1
% 8.08/1.49  --bmc1_max_bound_default                -1
% 8.08/1.49  --bmc1_symbol_reachability              true
% 8.08/1.49  --bmc1_property_lemmas                  false
% 8.08/1.49  --bmc1_k_induction                      false
% 8.08/1.49  --bmc1_non_equiv_states                 false
% 8.08/1.49  --bmc1_deadlock                         false
% 8.08/1.49  --bmc1_ucm                              false
% 8.08/1.49  --bmc1_add_unsat_core                   none
% 8.08/1.49  --bmc1_unsat_core_children              false
% 8.08/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.08/1.49  --bmc1_out_stat                         full
% 8.08/1.49  --bmc1_ground_init                      false
% 8.08/1.49  --bmc1_pre_inst_next_state              false
% 8.08/1.49  --bmc1_pre_inst_state                   false
% 8.08/1.49  --bmc1_pre_inst_reach_state             false
% 8.08/1.49  --bmc1_out_unsat_core                   false
% 8.08/1.49  --bmc1_aig_witness_out                  false
% 8.08/1.49  --bmc1_verbose                          false
% 8.08/1.49  --bmc1_dump_clauses_tptp                false
% 8.08/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.08/1.49  --bmc1_dump_file                        -
% 8.08/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.08/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.08/1.49  --bmc1_ucm_extend_mode                  1
% 8.08/1.49  --bmc1_ucm_init_mode                    2
% 8.08/1.49  --bmc1_ucm_cone_mode                    none
% 8.08/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.08/1.49  --bmc1_ucm_relax_model                  4
% 8.08/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.08/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.08/1.49  --bmc1_ucm_layered_model                none
% 8.08/1.49  --bmc1_ucm_max_lemma_size               10
% 8.08/1.49  
% 8.08/1.49  ------ AIG Options
% 8.08/1.49  
% 8.08/1.49  --aig_mode                              false
% 8.08/1.49  
% 8.08/1.49  ------ Instantiation Options
% 8.08/1.49  
% 8.08/1.49  --instantiation_flag                    true
% 8.08/1.49  --inst_sos_flag                         false
% 8.08/1.49  --inst_sos_phase                        true
% 8.08/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.08/1.49  --inst_lit_sel_side                     num_symb
% 8.08/1.49  --inst_solver_per_active                1400
% 8.08/1.49  --inst_solver_calls_frac                1.
% 8.08/1.49  --inst_passive_queue_type               priority_queues
% 8.08/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.08/1.49  --inst_passive_queues_freq              [25;2]
% 8.08/1.49  --inst_dismatching                      true
% 8.08/1.49  --inst_eager_unprocessed_to_passive     true
% 8.08/1.49  --inst_prop_sim_given                   true
% 8.08/1.49  --inst_prop_sim_new                     false
% 8.08/1.49  --inst_subs_new                         false
% 8.08/1.49  --inst_eq_res_simp                      false
% 8.08/1.49  --inst_subs_given                       false
% 8.08/1.49  --inst_orphan_elimination               true
% 8.08/1.49  --inst_learning_loop_flag               true
% 8.08/1.49  --inst_learning_start                   3000
% 8.08/1.49  --inst_learning_factor                  2
% 8.08/1.49  --inst_start_prop_sim_after_learn       3
% 8.08/1.49  --inst_sel_renew                        solver
% 8.08/1.49  --inst_lit_activity_flag                true
% 8.08/1.49  --inst_restr_to_given                   false
% 8.08/1.49  --inst_activity_threshold               500
% 8.08/1.49  --inst_out_proof                        true
% 8.08/1.49  
% 8.08/1.49  ------ Resolution Options
% 8.08/1.49  
% 8.08/1.49  --resolution_flag                       true
% 8.08/1.49  --res_lit_sel                           adaptive
% 8.08/1.49  --res_lit_sel_side                      none
% 8.08/1.49  --res_ordering                          kbo
% 8.08/1.49  --res_to_prop_solver                    active
% 8.08/1.49  --res_prop_simpl_new                    false
% 8.08/1.49  --res_prop_simpl_given                  true
% 8.08/1.49  --res_passive_queue_type                priority_queues
% 8.08/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.08/1.49  --res_passive_queues_freq               [15;5]
% 8.08/1.49  --res_forward_subs                      full
% 8.08/1.49  --res_backward_subs                     full
% 8.08/1.49  --res_forward_subs_resolution           true
% 8.08/1.49  --res_backward_subs_resolution          true
% 8.08/1.49  --res_orphan_elimination                true
% 8.08/1.49  --res_time_limit                        2.
% 8.08/1.49  --res_out_proof                         true
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Options
% 8.08/1.49  
% 8.08/1.49  --superposition_flag                    true
% 8.08/1.49  --sup_passive_queue_type                priority_queues
% 8.08/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.08/1.49  --sup_passive_queues_freq               [1;4]
% 8.08/1.49  --demod_completeness_check              fast
% 8.08/1.49  --demod_use_ground                      true
% 8.08/1.49  --sup_to_prop_solver                    passive
% 8.08/1.49  --sup_prop_simpl_new                    true
% 8.08/1.49  --sup_prop_simpl_given                  true
% 8.08/1.49  --sup_fun_splitting                     false
% 8.08/1.49  --sup_smt_interval                      50000
% 8.08/1.49  
% 8.08/1.49  ------ Superposition Simplification Setup
% 8.08/1.49  
% 8.08/1.49  --sup_indices_passive                   []
% 8.08/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.08/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 8.08/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_full_bw                           [BwDemod]
% 8.08/1.49  --sup_immed_triv                        [TrivRules]
% 8.08/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.08/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_immed_bw_main                     []
% 8.08/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.08/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.08/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.08/1.49  
% 8.08/1.49  ------ Combination Options
% 8.08/1.49  
% 8.08/1.49  --comb_res_mult                         3
% 8.08/1.49  --comb_sup_mult                         2
% 8.08/1.49  --comb_inst_mult                        10
% 8.08/1.49  
% 8.08/1.49  ------ Debug Options
% 8.08/1.49  
% 8.08/1.49  --dbg_backtrace                         false
% 8.08/1.49  --dbg_dump_prop_clauses                 false
% 8.08/1.49  --dbg_dump_prop_clauses_file            -
% 8.08/1.49  --dbg_out_stat                          false
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  ------ Proving...
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS status Theorem for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  fof(f16,conjecture,(
% 8.08/1.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f17,negated_conjecture,(
% 8.08/1.49    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 8.08/1.49    inference(negated_conjecture,[],[f16])).
% 8.08/1.49  
% 8.08/1.49  fof(f19,plain,(
% 8.08/1.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 8.08/1.49    inference(ennf_transformation,[],[f17])).
% 8.08/1.49  
% 8.08/1.49  fof(f25,plain,(
% 8.08/1.49    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 8.08/1.49    introduced(choice_axiom,[])).
% 8.08/1.49  
% 8.08/1.49  fof(f26,plain,(
% 8.08/1.49    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 8.08/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f25])).
% 8.08/1.49  
% 8.08/1.49  fof(f49,plain,(
% 8.08/1.49    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 8.08/1.49    inference(cnf_transformation,[],[f26])).
% 8.08/1.49  
% 8.08/1.49  fof(f7,axiom,(
% 8.08/1.49    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f33,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f7])).
% 8.08/1.49  
% 8.08/1.49  fof(f2,axiom,(
% 8.08/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f28,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.08/1.49    inference(cnf_transformation,[],[f2])).
% 8.08/1.49  
% 8.08/1.49  fof(f51,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f33,f28])).
% 8.08/1.49  
% 8.08/1.49  fof(f10,axiom,(
% 8.08/1.49    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f43,plain,(
% 8.08/1.49    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f10])).
% 8.08/1.49  
% 8.08/1.49  fof(f11,axiom,(
% 8.08/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f44,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f11])).
% 8.08/1.49  
% 8.08/1.49  fof(f12,axiom,(
% 8.08/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f45,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f12])).
% 8.08/1.49  
% 8.08/1.49  fof(f13,axiom,(
% 8.08/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f46,plain,(
% 8.08/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f13])).
% 8.08/1.49  
% 8.08/1.49  fof(f14,axiom,(
% 8.08/1.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f47,plain,(
% 8.08/1.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f14])).
% 8.08/1.49  
% 8.08/1.49  fof(f15,axiom,(
% 8.08/1.49    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f48,plain,(
% 8.08/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f15])).
% 8.08/1.49  
% 8.08/1.49  fof(f52,plain,(
% 8.08/1.49    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f47,f48])).
% 8.08/1.49  
% 8.08/1.49  fof(f53,plain,(
% 8.08/1.49    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f46,f52])).
% 8.08/1.49  
% 8.08/1.49  fof(f54,plain,(
% 8.08/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f45,f53])).
% 8.08/1.49  
% 8.08/1.49  fof(f55,plain,(
% 8.08/1.49    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f44,f54])).
% 8.08/1.49  
% 8.08/1.49  fof(f56,plain,(
% 8.08/1.49    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f43,f55])).
% 8.08/1.49  
% 8.08/1.49  fof(f68,plain,(
% 8.08/1.49    k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 8.08/1.49    inference(definition_unfolding,[],[f49,f51,f56,f56,f56])).
% 8.08/1.49  
% 8.08/1.49  fof(f9,axiom,(
% 8.08/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f42,plain,(
% 8.08/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 8.08/1.49    inference(cnf_transformation,[],[f9])).
% 8.08/1.49  
% 8.08/1.49  fof(f57,plain,(
% 8.08/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 8.08/1.49    inference(definition_unfolding,[],[f42,f51,f48,f56])).
% 8.08/1.49  
% 8.08/1.49  fof(f8,axiom,(
% 8.08/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 8.08/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.08/1.49  
% 8.08/1.49  fof(f18,plain,(
% 8.08/1.49    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 8.08/1.49    inference(ennf_transformation,[],[f8])).
% 8.08/1.49  
% 8.08/1.49  fof(f20,plain,(
% 8.08/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.08/1.49    inference(nnf_transformation,[],[f18])).
% 8.08/1.49  
% 8.08/1.49  fof(f21,plain,(
% 8.08/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.08/1.49    inference(flattening,[],[f20])).
% 8.08/1.49  
% 8.08/1.49  fof(f22,plain,(
% 8.08/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.08/1.49    inference(rectify,[],[f21])).
% 8.08/1.49  
% 8.08/1.49  fof(f23,plain,(
% 8.08/1.49    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 8.08/1.49    introduced(choice_axiom,[])).
% 8.08/1.49  
% 8.08/1.49  fof(f24,plain,(
% 8.08/1.49    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 8.08/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 8.08/1.49  
% 8.08/1.49  fof(f37,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.08/1.49    inference(cnf_transformation,[],[f24])).
% 8.08/1.49  
% 8.08/1.49  fof(f64,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.08/1.49    inference(definition_unfolding,[],[f37,f54])).
% 8.08/1.49  
% 8.08/1.49  fof(f69,plain,(
% 8.08/1.49    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 8.08/1.49    inference(equality_resolution,[],[f64])).
% 8.08/1.49  
% 8.08/1.49  fof(f70,plain,(
% 8.08/1.49    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X5))) )),
% 8.08/1.49    inference(equality_resolution,[],[f69])).
% 8.08/1.49  
% 8.08/1.49  fof(f34,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 8.08/1.49    inference(cnf_transformation,[],[f24])).
% 8.08/1.49  
% 8.08/1.49  fof(f67,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.08/1.49    inference(definition_unfolding,[],[f34,f54])).
% 8.08/1.49  
% 8.08/1.49  fof(f75,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))) )),
% 8.08/1.49    inference(equality_resolution,[],[f67])).
% 8.08/1.49  
% 8.08/1.49  fof(f35,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 8.08/1.49    inference(cnf_transformation,[],[f24])).
% 8.08/1.49  
% 8.08/1.49  fof(f66,plain,(
% 8.08/1.49    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_enumset1(X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 8.08/1.49    inference(definition_unfolding,[],[f35,f54])).
% 8.08/1.49  
% 8.08/1.49  fof(f73,plain,(
% 8.08/1.49    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_enumset1(X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 8.08/1.49    inference(equality_resolution,[],[f66])).
% 8.08/1.49  
% 8.08/1.49  fof(f74,plain,(
% 8.08/1.49    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_enumset1(X5,X5,X5,X5,X5,X1,X2))) )),
% 8.08/1.49    inference(equality_resolution,[],[f73])).
% 8.08/1.49  
% 8.08/1.49  fof(f50,plain,(
% 8.08/1.49    sK1 != sK2),
% 8.08/1.49    inference(cnf_transformation,[],[f26])).
% 8.08/1.49  
% 8.08/1.49  cnf(c_15,negated_conjecture,
% 8.08/1.49      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 8.08/1.49      inference(cnf_transformation,[],[f68]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_0,plain,
% 8.08/1.49      ( k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X6),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 8.08/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_787,plain,
% 8.08/1.49      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_15,c_0]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_10,plain,
% 8.08/1.49      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f70]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_216,plain,
% 8.08/1.49      ( r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X0)) = iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_26282,plain,
% 8.08/1.49      ( r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) = iProver_top ),
% 8.08/1.49      inference(superposition,[status(thm)],[c_787,c_216]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_13,plain,
% 8.08/1.49      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X2,X3))
% 8.08/1.49      | X0 = X1
% 8.08/1.49      | X0 = X2
% 8.08/1.49      | X0 = X3 ),
% 8.08/1.49      inference(cnf_transformation,[],[f75]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_346,plain,
% 8.08/1.49      ( ~ r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2))
% 8.08/1.49      | sK2 = X0
% 8.08/1.49      | sK2 = X1
% 8.08/1.49      | sK2 = X2 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_347,plain,
% 8.08/1.49      ( sK2 = X0
% 8.08/1.49      | sK2 = X1
% 8.08/1.49      | sK2 = X2
% 8.08/1.49      | r2_hidden(sK2,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 8.08/1.49      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_349,plain,
% 8.08/1.49      ( sK2 = sK1
% 8.08/1.49      | r2_hidden(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) != iProver_top ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_347]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_87,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_304,plain,
% 8.08/1.49      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_87]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_305,plain,
% 8.08/1.49      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_304]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_12,plain,
% 8.08/1.49      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) ),
% 8.08/1.49      inference(cnf_transformation,[],[f74]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_20,plain,
% 8.08/1.49      ( r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_17,plain,
% 8.08/1.49      ( ~ r2_hidden(sK1,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 8.08/1.49      | sK1 = sK1 ),
% 8.08/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(c_14,negated_conjecture,
% 8.08/1.49      ( sK1 != sK2 ),
% 8.08/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.08/1.49  
% 8.08/1.49  cnf(contradiction,plain,
% 8.08/1.49      ( $false ),
% 8.08/1.49      inference(minisat,
% 8.08/1.49                [status(thm)],
% 8.08/1.49                [c_26282,c_349,c_305,c_20,c_17,c_14]) ).
% 8.08/1.49  
% 8.08/1.49  
% 8.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.08/1.49  
% 8.08/1.49  ------                               Statistics
% 8.08/1.49  
% 8.08/1.49  ------ Selected
% 8.08/1.49  
% 8.08/1.49  total_time:                             0.978
% 8.08/1.49  
%------------------------------------------------------------------------------
